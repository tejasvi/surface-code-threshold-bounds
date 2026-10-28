import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15176 = true := by
  decide +kernel

theorem tot15176 : totK PD2M8K2 D2M8K2.t15176 = [0, 0, 207204992167, 486147934340, 175110057046, 10495943674, 0, 0] := by
  decide +kernel

theorem rows15177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15177 = true := by
  decide +kernel

theorem tot15177 : totK PD2M8K2 D2M8K2.t15177 = [0, 159521618790, 450409576749, 272880694255, 31137448343, 1556668195, 0, 0] := by
  decide +kernel

theorem rows15178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15178 = true := by
  decide +kernel

theorem tot15178 : totK PD2M8K2 D2M8K2.t15178 = [0, 171849923245, 446344649947, 254813402714, 18865771023, 0, 0, 0] := by
  decide +kernel

theorem rows15179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15179 = true := by
  decide +kernel

theorem tot15179 : totK PD2M8K2 D2M8K2.t15179 = [0, 92197201596, 358482215412, 368593995690, 70452379105, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
