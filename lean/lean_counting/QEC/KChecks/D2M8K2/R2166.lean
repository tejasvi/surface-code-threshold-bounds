import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8664 = true := by
  decide +kernel

theorem tot8664 : totK PD2M8K2 D2M8K2.t8664 = [0, 0, 295892144170, 488710961828, 103235102939, 1242138600, 0, 0] := by
  decide +kernel

theorem rows8665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8665 = true := by
  decide +kernel

theorem tot8665 : totK PD2M8K2 D2M8K2.t8665 = [0, 0, 207782562154, 473068375693, 166724116041, 7182288656, 0, 0] := by
  decide +kernel

theorem rows8666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8666 = true := by
  decide +kernel

theorem tot8666 : totK PD2M8K2 D2M8K2.t8666 = [0, 157380724936, 332957645211, 283896064605, 133393177065, 13326740810, 0, 0] := by
  decide +kernel

theorem rows8667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8667 = true := by
  decide +kernel

theorem tot8667 : totK PD2M8K2 D2M8K2.t8667 = [0, 180559822862, 470512075432, 240387305543, 15688808452, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
