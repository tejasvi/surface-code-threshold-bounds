import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13480 = true := by
  decide +kernel

theorem tot13480 : totK PD2M8K2 D2M8K2.t13480 = [0, 0, 0, 217761526514, 484761804747, 152012021027, 8002639606, 0] := by
  decide +kernel

theorem rows13481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13481 = true := by
  decide +kernel

theorem tot13481 : totK PD2M8K2 D2M8K2.t13481 = [0, 0, 83423316472, 312309405926, 364598158807, 98670361828, 4906626486, 0] := by
  decide +kernel

theorem rows13482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13482 = true := by
  decide +kernel

theorem tot13482 : totK PD2M8K2 D2M8K2.t13482 = [0, 0, 177805549595, 459404839495, 251590915656, 19272194432, 0, 0] := by
  decide +kernel

theorem rows13483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13483 = true := by
  decide +kernel

theorem tot13483 : totK PD2M8K2 D2M8K2.t13483 = [0, 0, 155553063228, 449659706804, 266115028169, 16572833544, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
