import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14184 = true := by
  decide +kernel

theorem tot14184 : totK PD2M8K2 D2M8K2.t14184 = [0, 182065017174, 438328309957, 258868305450, 30866666322, 0, 0, 0] := by
  decide +kernel

theorem rows14185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14185 = true := by
  decide +kernel

theorem tot14185 : totK PD2M8K2 D2M8K2.t14185 = [0, 195427136089, 471718174803, 220419345257, 15658503976, 0, 0, 0] := by
  decide +kernel

theorem rows14186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14186 = true := by
  decide +kernel

theorem tot14186 : totK PD2M8K2 D2M8K2.t14186 = [0, 0, 357028883736, 487395332144, 57483626712, 0, 0, 0] := by
  decide +kernel

theorem rows14187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14187 = true := by
  decide +kernel

theorem tot14187 : totK PD2M8K2 D2M8K2.t14187 = [0, 124274589184, 356253362749, 334496470944, 81491430889, 1415142070, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
