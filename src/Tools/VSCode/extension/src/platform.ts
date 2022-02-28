'use strict';

import * as os from 'os'


/* platform family */

export function is_windows(): boolean
{
  return os.type().startsWith("Windows")
}

export function is_linux(): boolean
{
  return os.type().startsWith("Linux")
}

export function is_macos(): boolean
{
  return os.type().startsWith("Darwin")
}

export function is_unix(): boolean
{
  return is_linux() || is_macos()
}
