import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12192 = true := by
  decide +kernel

theorem tot12192 : totK PD2M8K2 D2M8K2.t12192 = [0, 209762116988, 493227405201, 194312654160, 5463989431, 0, 0, 0] := by
  decide +kernel

theorem rows12193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12193 = true := by
  decide +kernel

theorem tot12193 : totK PD2M8K2 D2M8K2.t12193 = [0, 162835983161, 455030677283, 240070354506, 13452000861, 0, 0, 0] := by
  decide +kernel

theorem rows12194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12194 = true := by
  decide +kernel

theorem tot12194 : totK PD2M8K2 D2M8K2.t12194 = [0, 177611214225, 472686599338, 233920498134, 13115571915, 0, 0, 0] := by
  decide +kernel

theorem rows12195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12195 = true := by
  decide +kernel

theorem tot12195 : totK PD2M8K2 D2M8K2.t12195 = [0, 186467493710, 465359177515, 219750771012, 12319708528, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
