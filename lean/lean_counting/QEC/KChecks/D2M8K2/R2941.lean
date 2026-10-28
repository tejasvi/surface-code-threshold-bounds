import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11764 = true := by
  decide +kernel

theorem tot11764 : totK PD2M8K2 D2M8K2.t11764 = [0, 70106018420, 237246019186, 390467369827, 180286223310, 8170814383, 0, 0] := by
  decide +kernel

theorem rows11765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11765 = true := by
  decide +kernel

theorem tot11765 : totK PD2M8K2 D2M8K2.t11765 = [0, 182755172275, 471868768257, 256680741437, 23167459586, 0, 0, 0] := by
  decide +kernel

theorem rows11766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11766 = true := by
  decide +kernel

theorem tot11766 : totK PD2M8K2 D2M8K2.t11766 = [0, 171243662000, 456733757916, 241747674420, 15008140634, 0, 0, 0] := by
  decide +kernel

theorem rows11767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11767 = true := by
  decide +kernel

theorem tot11767 : totK PD2M8K2 D2M8K2.t11767 = [0, 0, 273455959912, 499014603833, 130872654903, 5998727602, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
