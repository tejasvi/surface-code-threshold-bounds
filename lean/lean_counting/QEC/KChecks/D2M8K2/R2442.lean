import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9768 = true := by
  decide +kernel

theorem tot9768 : totK PD2M8K2 D2M8K2.t9768 = [0, 169604885810, 456548325490, 244978119323, 12902863657, 0, 0, 0] := by
  decide +kernel

theorem rows9769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9769 = true := by
  decide +kernel

theorem tot9769 : totK PD2M8K2 D2M8K2.t9769 = [0, 0, 227527226284, 499870569139, 148105367369, 7166294683, 0, 0] := by
  decide +kernel

theorem rows9770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9770 = true := by
  decide +kernel

theorem tot9770 : totK PD2M8K2 D2M8K2.t9770 = [0, 80007408125, 280595501698, 383565995937, 117555409871, 5883432551, 0, 0] := by
  decide +kernel

theorem rows9771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9771 = true := by
  decide +kernel

theorem tot9771 : totK PD2M8K2 D2M8K2.t9771 = [0, 164885921400, 472492464749, 257212332055, 19565923523, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
