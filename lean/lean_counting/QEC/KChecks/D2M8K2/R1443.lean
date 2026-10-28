import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5772 = true := by
  decide +kernel

theorem tot5772 : totK PD2M8K2 D2M8K2.t5772 = [0, 0, 242233170838, 501581860741, 142279837344, 4030866388, 0, 0] := by
  decide +kernel

theorem rows5773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5773 = true := by
  decide +kernel

theorem tot5773 : totK PD2M8K2 D2M8K2.t5773 = [0, 172096877105, 465298970582, 259877167963, 28147611709, 0, 0, 0] := by
  decide +kernel

theorem rows5774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5774 = true := by
  decide +kernel

theorem tot5774 : totK PD2M8K2 D2M8K2.t5774 = [0, 173415170840, 446982357520, 263135668355, 18787643879, 0, 0, 0] := by
  decide +kernel

theorem rows5775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5775 = true := by
  decide +kernel

theorem tot5775 : totK PD2M8K2 D2M8K2.t5775 = [0, 93773531552, 354794875381, 377112696246, 75087336690, 1249641317, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
