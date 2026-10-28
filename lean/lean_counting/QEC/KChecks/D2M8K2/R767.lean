import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3068 = true := by
  decide +kernel

theorem tot3068 : totK PD2M8K2 D2M8K2.t3068 = [0, 0, 200685077174, 480571389435, 171575629848, 7392550509, 0, 0] := by
  decide +kernel

theorem rows3069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3069 = true := by
  decide +kernel

theorem tot3069 : totK PD2M8K2 D2M8K2.t3069 = [0, 0, 0, 317588657850, 435881485466, 64485287002, 1103454931, 0] := by
  decide +kernel

theorem rows3070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3070 = true := by
  decide +kernel

theorem tot3070 : totK PD2M8K2 D2M8K2.t3070 = [0, 0, 178006512081, 462664561132, 239078741511, 15063360013, 0, 0] := by
  decide +kernel

theorem rows3071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3071 = true := by
  decide +kernel

theorem tot3071 : totK PD2M8K2 D2M8K2.t3071 = [0, 0, 254474883780, 469102550947, 178414424008, 6725739876, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
