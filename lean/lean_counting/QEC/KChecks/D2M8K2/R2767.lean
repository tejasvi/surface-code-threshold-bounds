import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11068 = true := by
  decide +kernel

theorem tot11068 : totK PD2M8K2 D2M8K2.t11068 = [0, 197380716886, 483730283063, 214793528934, 12606907924, 0, 0, 0] := by
  decide +kernel

theorem rows11069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11069 = true := by
  decide +kernel

theorem tot11069 : totK PD2M8K2 D2M8K2.t11069 = [0, 198513504280, 477051674682, 215601748973, 11051716772, 0, 0, 0] := by
  decide +kernel

theorem rows11070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11070 = true := by
  decide +kernel

theorem tot11070 : totK PD2M8K2 D2M8K2.t11070 = [0, 182244254430, 471103095941, 221763680499, 12370590376, 0, 0, 0] := by
  decide +kernel

theorem rows11071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11071 = true := by
  decide +kernel

theorem tot11071 : totK PD2M8K2 D2M8K2.t11071 = [0, 164890849328, 469249760156, 240929897217, 13419997576, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
