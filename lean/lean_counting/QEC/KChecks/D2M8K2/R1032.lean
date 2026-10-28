import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4128 = true := by
  decide +kernel

theorem tot4128 : totK PD2M8K2 D2M8K2.t4128 = [0, 126267617790, 446042188044, 294558916139, 23470772497, 0, 0, 0] := by
  decide +kernel

theorem rows4129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4129 = true := by
  decide +kernel

theorem tot4129 : totK PD2M8K2 D2M8K2.t4129 = [0, 77585768145, 368733656574, 420240347264, 48018659151, 0, 0, 0] := by
  decide +kernel

theorem rows4130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4130 = true := by
  decide +kernel

theorem tot4130 : totK PD2M8K2 D2M8K2.t4130 = [0, 169129356820, 438136019023, 281459818040, 30474664319, 0, 0, 0] := by
  decide +kernel

theorem rows4131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4131 = true := by
  decide +kernel

theorem tot4131 : totK PD2M8K2 D2M8K2.t4131 = [0, 179880361390, 485692171673, 236696992072, 12394439879, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
