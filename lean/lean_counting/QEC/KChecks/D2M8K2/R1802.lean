import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7208 = true := by
  decide +kernel

theorem tot7208 : totK PD2M8K2 D2M8K2.t7208 = [0, 0, 179163009487, 478491228428, 237072860639, 11629362197, 0, 0] := by
  decide +kernel

theorem rows7209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7209 = true := by
  decide +kernel

theorem tot7209 : totK PD2M8K2 D2M8K2.t7209 = [0, 0, 0, 289155986295, 492658291970, 103805206587, 1242138600, 0] := by
  decide +kernel

theorem rows7210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7210 = true := by
  decide +kernel

theorem tot7210 : totK PD2M8K2 D2M8K2.t7210 = [0, 0, 55649345463, 244505646709, 398535417792, 172829079397, 12544355448, 0] := by
  decide +kernel

theorem rows7211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7211 = true := by
  decide +kernel

theorem tot7211 : totK PD2M8K2 D2M8K2.t7211 = [0, 0, 191419347429, 490598445797, 208736993864, 9852138406, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
