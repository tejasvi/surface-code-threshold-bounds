import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5116 = true := by
  decide +kernel

theorem tot5116 : totK PD2M8K2 D2M8K2.t5116 = [0, 0, 193126047439, 460154230275, 235036421492, 15098262976, 0, 0] := by
  decide +kernel

theorem rows5117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5117 = true := by
  decide +kernel

theorem tot5117 : totK PD2M8K2 D2M8K2.t5117 = [0, 0, 189736706310, 450412143747, 227187908392, 17104814242, 0, 0] := by
  decide +kernel

theorem rows5118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5118 = true := by
  decide +kernel

theorem tot5118 : totK PD2M8K2 D2M8K2.t5118 = [0, 0, 37477818724, 351671467575, 428509037134, 66491293268, 1096505104, 0] := by
  decide +kernel

theorem rows5119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5119 = true := by
  decide +kernel

theorem tot5119 : totK PD2M8K2 D2M8K2.t5119 = [0, 0, 94305354095, 393394878487, 393199260593, 38624908518, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
