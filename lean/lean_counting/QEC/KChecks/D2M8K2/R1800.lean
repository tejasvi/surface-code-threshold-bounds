import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7200 = true := by
  decide +kernel

theorem tot7200 : totK PD2M8K2 D2M8K2.t7200 = [0, 0, 180198236777, 468485761912, 252100449599, 17622407247, 0, 0] := by
  decide +kernel

theorem rows7201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7201 = true := by
  decide +kernel

theorem tot7201 : totK PD2M8K2 D2M8K2.t7201 = [0, 0, 195890711451, 476195843262, 226742174771, 14651902506, 0, 0] := by
  decide +kernel

theorem rows7202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7202 = true := by
  decide +kernel

theorem tot7202 : totK PD2M8K2 D2M8K2.t7202 = [0, 0, 192135926335, 474823003254, 210604640551, 12032668289, 0, 0] := by
  decide +kernel

theorem rows7203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7203 = true := by
  decide +kernel

theorem tot7203 : totK PD2M8K2 D2M8K2.t7203 = [0, 0, 0, 306331167111, 491055455712, 83114625579, 1075657031, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
