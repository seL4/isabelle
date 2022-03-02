/*  Author:     Makarius

File-system operations (see Pure/General/file.scala)
*/

'use strict';

import * as fs from 'fs/promises'
import { Buffer } from 'buffer'


export async function read_bytes(path: string): Promise<Buffer>
{
    return fs.readFile(path)
}

export async function read(path: string): Promise<string>
{
    return read_bytes(path).then(buffer => buffer.toString())
}

export async function read_json<T>(path: string): Promise<T>
{
    return read(path).then(JSON.parse) as Promise<T>
}
