import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5180 = true := by
  decide +kernel

theorem tot5180 : totK PD2M8K2 D2M8K2.t5180 = [0, 0, 179739888451, 429766765507, 284929288228, 27483786287, 0, 0] := by
  decide +kernel

theorem rows5181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5181 = true := by
  decide +kernel

theorem tot5181 : totK PD2M8K2 D2M8K2.t5181 = [0, 0, 175727005596, 457437463095, 248437157932, 17977461628, 0, 0] := by
  decide +kernel

theorem rows5182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5182 = true := by
  decide +kernel

theorem tot5182 : totK PD2M8K2 D2M8K2.t5182 = [0, 0, 69515879333, 344063422612, 371626042266, 116317871756, 13059052111, 0] := by
  decide +kernel

theorem rows5183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5183 = true := by
  decide +kernel

theorem tot5183 : totK PD2M8K2 D2M8K2.t5183 = [0, 0, 0, 191341217191, 480215735379, 203174044477, 9242510550, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
