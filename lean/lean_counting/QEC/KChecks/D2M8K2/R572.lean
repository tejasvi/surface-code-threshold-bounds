import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2288 = true := by
  decide +kernel

theorem tot2288 : totK PD2M8K2 D2M8K2.t2288 = [0, 0, 184110442286, 465502984638, 224913002268, 17080783126, 0, 0] := by
  decide +kernel

theorem rows2289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2289 = true := by
  decide +kernel

theorem tot2289 : totK PD2M8K2 D2M8K2.t2289 = [0, 0, 173576560399, 472309328716, 222120867091, 10797020908, 0, 0] := by
  decide +kernel

theorem rows2290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2290 = true := by
  decide +kernel

theorem tot2290 : totK PD2M8K2 D2M8K2.t2290 = [0, 0, 170591022402, 448054435675, 234675769609, 17439945043, 0, 0] := by
  decide +kernel

theorem rows2291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2291 = true := by
  decide +kernel

theorem tot2291 : totK PD2M8K2 D2M8K2.t2291 = [0, 0, 0, 290332503190, 461774354350, 108908941229, 1369150432, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
