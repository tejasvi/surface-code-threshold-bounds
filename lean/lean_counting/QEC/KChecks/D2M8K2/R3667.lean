import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14668 = true := by
  decide +kernel

theorem tot14668 : totK PD2M8K2 D2M8K2.t14668 = [0, 0, 188187684927, 473017588217, 206275266774, 12573569609, 0, 0] := by
  decide +kernel

theorem rows14669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14669 = true := by
  decide +kernel

theorem tot14669 : totK PD2M8K2 D2M8K2.t14669 = [0, 0, 214600620317, 461912778145, 173723985529, 9656040098, 0, 0] := by
  decide +kernel

theorem rows14670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14670 = true := by
  decide +kernel

theorem tot14670 : totK PD2M8K2 D2M8K2.t14670 = [0, 0, 84910640420, 395277381740, 315773405726, 49886752533, 1217496766, 0] := by
  decide +kernel

theorem rows14671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14671 = true := by
  decide +kernel

theorem tot14671 : totK PD2M8K2 D2M8K2.t14671 = [0, 0, 19982995165, 326035470801, 446581175464, 59200094971, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
