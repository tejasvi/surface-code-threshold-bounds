import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2972 = true := by
  decide +kernel

theorem tot2972 : totK PD2M8K2 D2M8K2.t2972 = [0, 176571808633, 463330482911, 239781192335, 13889774375, 0, 0, 0] := by
  decide +kernel

theorem rows2973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2973 = true := by
  decide +kernel

theorem tot2973 : totK PD2M8K2 D2M8K2.t2973 = [0, 86750274188, 335894488432, 387931144391, 80244811323, 1164319620, 0, 0] := by
  decide +kernel

theorem rows2974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2974 = true := by
  decide +kernel

theorem tot2974 : totK PD2M8K2 D2M8K2.t2974 = [0, 0, 227411880493, 475983549162, 163238897460, 9404247146, 0, 0] := by
  decide +kernel

theorem rows2975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2975 = true := by
  decide +kernel

theorem tot2975 : totK PD2M8K2 D2M8K2.t2975 = [0, 153473951145, 408949792726, 271600925172, 53475964396, 2481160468, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
