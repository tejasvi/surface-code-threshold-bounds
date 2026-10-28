import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7268 = true := by
  decide +kernel

theorem tot7268 : totK PD2M8K2 D2M8K2.t7268 = [0, 0, 117887320124, 431208021742, 327065384934, 27379333618, 0, 0] := by
  decide +kernel

theorem rows7269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7269 = true := by
  decide +kernel

theorem tot7269 : totK PD2M8K2 D2M8K2.t7269 = [0, 0, 203843382585, 453979315295, 243381875839, 17513443745, 0, 0] := by
  decide +kernel

theorem rows7270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7270 = true := by
  decide +kernel

theorem tot7270 : totK PD2M8K2 D2M8K2.t7270 = [0, 0, 188652142637, 478550330516, 225784276390, 14967974183, 0, 0] := by
  decide +kernel

theorem rows7271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7271 = true := by
  decide +kernel

theorem tot7271 : totK PD2M8K2 D2M8K2.t7271 = [0, 0, 181426854409, 441008093951, 226166481702, 17115888737, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
