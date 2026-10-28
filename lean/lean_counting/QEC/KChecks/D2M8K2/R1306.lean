import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5224 = true := by
  decide +kernel

theorem tot5224 : totK PD2M8K2 D2M8K2.t5224 = [0, 0, 196090478089, 470474908207, 213548606195, 14707859566, 0, 0] := by
  decide +kernel

theorem rows5225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5225 = true := by
  decide +kernel

theorem tot5225 : totK PD2M8K2 D2M8K2.t5225 = [0, 0, 155948194005, 473796967506, 223281021950, 9452343410, 0, 0] := by
  decide +kernel

theorem rows5226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5226 = true := by
  decide +kernel

theorem tot5226 : totK PD2M8K2 D2M8K2.t5226 = [0, 0, 88265605660, 348089318970, 356693128141, 78807037190, 1369150432, 0] := by
  decide +kernel

theorem rows5227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5227 = true := by
  decide +kernel

theorem tot5227 : totK PD2M8K2 D2M8K2.t5227 = [0, 0, 47226083768, 364443313776, 420564180511, 39641994028, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
