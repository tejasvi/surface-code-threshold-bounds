import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15404 = true := by
  decide +kernel

theorem tot15404 : totK PD2M8K2 D2M8K2.t15404 = [0, 85501138483, 293856124129, 330471396627, 174709733521, 16297041788, 0, 0] := by
  decide +kernel

theorem rows15405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15405 = true := by
  decide +kernel

theorem tot15405 : totK PD2M8K2 D2M8K2.t15405 = [0, 202594001042, 472929317997, 216344077947, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows15406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15406 = true := by
  decide +kernel

theorem tot15406 : totK PD2M8K2 D2M8K2.t15406 = [0, 37445179589, 317501345424, 445079538677, 93741682510, 1369150432, 0, 0] := by
  decide +kernel

theorem rows15407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15407 = true := by
  decide +kernel

theorem tot15407 : totK PD2M8K2 D2M8K2.t15407 = [0, 93574619190, 380984839330, 402856766695, 51770044017, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
