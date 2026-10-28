import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15040 = true := by
  decide +kernel

theorem tot15040 : totK PD2M8K2 D2M8K2.t15040 = [0, 104139918814, 363684640153, 351806350378, 68992664317, 946121569, 0, 0] := by
  decide +kernel

theorem rows15041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15041 = true := by
  decide +kernel

theorem tot15041 : totK PD2M8K2 D2M8K2.t15041 = [0, 170544862733, 435297929847, 277609411253, 29969113215, 0, 0, 0] := by
  decide +kernel

theorem rows15042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15042 = true := by
  decide +kernel

theorem tot15042 : totK PD2M8K2 D2M8K2.t15042 = [0, 146966136639, 452351995574, 284627828107, 21763210178, 0, 0, 0] := by
  decide +kernel

theorem rows15043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15043 = true := by
  decide +kernel

theorem tot15043 : totK PD2M8K2 D2M8K2.t15043 = [0, 0, 204701689024, 484550496280, 178887421323, 7680527984, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
