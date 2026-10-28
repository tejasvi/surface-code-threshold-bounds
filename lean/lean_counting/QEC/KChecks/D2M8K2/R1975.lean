import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7900 = true := by
  decide +kernel

theorem tot7900 : totK PD2M8K2 D2M8K2.t7900 = [0, 0, 92388563553, 408046466517, 363634858201, 36374450986, 0, 0] := by
  decide +kernel

theorem rows7901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7901 = true := by
  decide +kernel

theorem tot7901 : totK PD2M8K2 D2M8K2.t7901 = [0, 0, 189713657323, 472056709166, 232383453395, 15842369551, 0, 0] := by
  decide +kernel

theorem rows7902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7902 = true := by
  decide +kernel

theorem tot7902 : totK PD2M8K2 D2M8K2.t7902 = [0, 0, 205005166367, 485774130657, 200217373420, 10187124135, 0, 0] := by
  decide +kernel

theorem rows7903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7903 = true := by
  decide +kernel

theorem tot7903 : totK PD2M8K2 D2M8K2.t7903 = [0, 0, 180324224485, 480015004977, 238082128269, 12662259608, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
