import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2820 = true := by
  decide +kernel

theorem tot2820 : totK PD2M8K2 D2M8K2.t2820 = [94308027437, 305393327910, 357514576617, 155464248141, 13468148062, 0, 0, 0] := by
  decide +kernel

theorem rows2821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2821 = true := by
  decide +kernel

theorem tot2821 : totK PD2M8K2 D2M8K2.t2821 = [187440663317, 457393712883, 250357258995, 19937176192, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2822 = true := by
  decide +kernel

theorem tot2822 : totK PD2M8K2 D2M8K2.t2822 = [163342843260, 462751926803, 269246824354, 27830078316, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2823 = true := by
  decide +kernel

theorem tot2823 : totK PD2M8K2 D2M8K2.t2823 = [0, 182196439201, 451050570117, 252589806364, 25373788367, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
