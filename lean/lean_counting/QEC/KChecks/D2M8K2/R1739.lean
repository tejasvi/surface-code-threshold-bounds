import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6956 = true := by
  decide +kernel

theorem tot6956 : totK PD2M8K2 D2M8K2.t6956 = [0, 168467805187, 474249906226, 255923177717, 17360819134, 0, 0, 0] := by
  decide +kernel

theorem rows6957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6957 = true := by
  decide +kernel

theorem tot6957 : totK PD2M8K2 D2M8K2.t6957 = [0, 0, 173184595800, 446393090539, 258406205486, 23329198674, 0, 0] := by
  decide +kernel

theorem rows6958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6958 = true := by
  decide +kernel

theorem tot6958 : totK PD2M8K2 D2M8K2.t6958 = [0, 0, 224993218165, 501870447287, 167311483900, 2655688651, 0, 0] := by
  decide +kernel

theorem rows6959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6959 = true := by
  decide +kernel

theorem tot6959 : totK PD2M8K2 D2M8K2.t6959 = [0, 175012022416, 394399802099, 229977355949, 100548502633, 6779944490, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
