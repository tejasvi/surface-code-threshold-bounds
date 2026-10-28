import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12604 = true := by
  decide +kernel

theorem tot12604 : totK PD2M8K2 D2M8K2.t12604 = [0, 0, 286243802545, 510724175485, 103487100773, 1369150432, 0, 0] := by
  decide +kernel

theorem rows12605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12605 = true := by
  decide +kernel

theorem tot12605 : totK PD2M8K2 D2M8K2.t12605 = [0, 154567988930, 437163926645, 287438297324, 29717057072, 0, 0, 0] := by
  decide +kernel

theorem rows12606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12606 = true := by
  decide +kernel

theorem tot12606 : totK PD2M8K2 D2M8K2.t12606 = [0, 201357391235, 459361250790, 213038483147, 14470573824, 0, 0, 0] := by
  decide +kernel

theorem rows12607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12607 = true := by
  decide +kernel

theorem tot12607 : totK PD2M8K2 D2M8K2.t12607 = [0, 45376043749, 320160232257, 441572993389, 91339345027, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
