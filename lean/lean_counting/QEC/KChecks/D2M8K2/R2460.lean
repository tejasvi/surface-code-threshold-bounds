import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9840 = true := by
  decide +kernel

theorem tot9840 : totK PD2M8K2 D2M8K2.t9840 = [0, 0, 221159238703, 503795276070, 166760596815, 4777472366, 0, 0] := by
  decide +kernel

theorem rows9841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9841 = true := by
  decide +kernel

theorem tot9841 : totK PD2M8K2 D2M8K2.t9841 = [0, 0, 198098248819, 465332497988, 210295846819, 12889932489, 0, 0] := by
  decide +kernel

theorem rows9842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9842 = true := by
  decide +kernel

theorem tot9842 : totK PD2M8K2 D2M8K2.t9842 = [0, 0, 190518778063, 483829050058, 202537715305, 9713690252, 0, 0] := by
  decide +kernel

theorem rows9843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9843 = true := by
  decide +kernel

theorem tot9843 : totK PD2M8K2 D2M8K2.t9843 = [0, 0, 86510406232, 374712566630, 347153020327, 56394390424, 1239866073, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
