import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14728 = true := by
  decide +kernel

theorem tot14728 : totK PD2M8K2 D2M8K2.t14728 = [0, 75883481715, 342352356648, 397657061374, 92814145929, 1268739303, 0, 0] := by
  decide +kernel

theorem rows14729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14729 = true := by
  decide +kernel

theorem tot14729 : totK PD2M8K2 D2M8K2.t14729 = [0, 0, 223391212661, 495420645336, 164245346041, 4698297300, 0, 0] := by
  decide +kernel

theorem rows14730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14730 = true := by
  decide +kernel

theorem tot14730 : totK PD2M8K2 D2M8K2.t14730 = [92089433884, 207014642245, 164122499684, 265394896165, 156551161189, 14967743524, 0, 0] := by
  decide +kernel

theorem rows14731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14731 = true := by
  decide +kernel

theorem tot14731 : totK PD2M8K2 D2M8K2.t14731 = [174081179172, 463491292296, 244063837446, 17115888737, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
