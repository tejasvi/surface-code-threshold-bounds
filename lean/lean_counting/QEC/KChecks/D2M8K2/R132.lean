import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t528 = true := by
  decide +kernel

theorem tot528 : totK PD2M8K2 D2M8K2.t528 = [0, 0, 185714772691, 476967884020, 219364961159, 12183533023, 0, 0] := by
  decide +kernel

theorem rows529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t529 = true := by
  decide +kernel

theorem tot529 : totK PD2M8K2 D2M8K2.t529 = [0, 0, 51704052093, 334136295810, 405003594276, 80705884854, 1162935789, 0] := by
  decide +kernel

theorem rows530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t530 = true := by
  decide +kernel

theorem tot530 : totK PD2M8K2 D2M8K2.t530 = [0, 0, 0, 198982145677, 451529005976, 184725297204, 11853261585, 0] := by
  decide +kernel

theorem rows531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t531 = true := by
  decide +kernel

theorem tot531 : totK PD2M8K2 D2M8K2.t531 = [0, 0, 167339488237, 448714599341, 233231756638, 23111091670, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
