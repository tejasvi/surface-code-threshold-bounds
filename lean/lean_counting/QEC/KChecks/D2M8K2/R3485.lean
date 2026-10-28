import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13940 = true := by
  decide +kernel

theorem tot13940 : totK PD2M8K2 D2M8K2.t13940 = [0, 174673355794, 474386713690, 245379950093, 21294040362, 0, 0, 0] := by
  decide +kernel

theorem rows13941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13941 = true := by
  decide +kernel

theorem tot13941 : totK PD2M8K2 D2M8K2.t13941 = [0, 157796901861, 441226633818, 268525258929, 22458950245, 0, 0, 0] := by
  decide +kernel

theorem rows13942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13942 = true := by
  decide +kernel

theorem tot13942 : totK PD2M8K2 D2M8K2.t13942 = [0, 89165724567, 352415462973, 373511976873, 68244088140, 1075657031, 0, 0] := by
  decide +kernel

theorem rows13943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13943 = true := by
  decide +kernel

theorem tot13943 : totK PD2M8K2 D2M8K2.t13943 = [0, 0, 295082065814, 469565373170, 106539681481, 3804183361, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
