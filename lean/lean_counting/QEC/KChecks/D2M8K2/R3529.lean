import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14116 = true := by
  decide +kernel

theorem tot14116 : totK PD2M8K2 D2M8K2.t14116 = [0, 0, 80424458176, 348748518321, 363639241812, 74089412277, 1332468113, 0] := by
  decide +kernel

theorem rows14117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14117 = true := by
  decide +kernel

theorem tot14117 : totK PD2M8K2 D2M8K2.t14117 = [0, 0, 174694634913, 445745230825, 264427733576, 23683559190, 0, 0] := by
  decide +kernel

theorem rows14118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14118 = true := by
  decide +kernel

theorem tot14118 : totK PD2M8K2 D2M8K2.t14118 = [0, 0, 178493127927, 467134349311, 247437852073, 11486445924, 0, 0] := by
  decide +kernel

theorem rows14119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14119 = true := by
  decide +kernel

theorem tot14119 : totK PD2M8K2 D2M8K2.t14119 = [0, 0, 0, 287729738140, 491516556268, 95636926616, 1229550402, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
