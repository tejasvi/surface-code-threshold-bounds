import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4012 = true := by
  decide +kernel

theorem tot4012 : totK PD2M8K2 D2M8K2.t4012 = [0, 0, 185715954455, 467664246809, 229273230201, 12445855870, 0, 0] := by
  decide +kernel

theorem rows4013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4013 = true := by
  decide +kernel

theorem tot4013 : totK PD2M8K2 D2M8K2.t4013 = [0, 0, 56695548609, 320970274437, 418491413646, 90196013648, 1242138600, 0] := by
  decide +kernel

theorem rows4014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4014 = true := by
  decide +kernel

theorem tot4014 : totK PD2M8K2 D2M8K2.t4014 = [0, 0, 0, 219351927854, 462202214077, 161673088504, 7182288656, 0] := by
  decide +kernel

theorem rows4015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4015 = true := by
  decide +kernel

theorem tot4015 : totK PD2M8K2 D2M8K2.t4015 = [0, 94445126902, 239990604536, 221465454530, 221589303317, 128761825349, 13326740810, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
