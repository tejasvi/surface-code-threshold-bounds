import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4328 = true := by
  decide +kernel

theorem tot4328 : totK PD2M8K2 D2M8K2.t4328 = [0, 0, 0, 179507293509, 466223851584, 244841535179, 11208571120, 0] := by
  decide +kernel

theorem rows4329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4329 = true := by
  decide +kernel

theorem tot4329 : totK PD2M8K2 D2M8K2.t4329 = [0, 0, 0, 204769706161, 500803323497, 181649105160, 3886101548, 0] := by
  decide +kernel

theorem rows4330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4330 = true := by
  decide +kernel

theorem tot4330 : totK PD2M8K2 D2M8K2.t4330 = [0, 0, 0, 178913279218, 451061675784, 247084470963, 21288891614, 0] := by
  decide +kernel

theorem rows4331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4331 = true := by
  decide +kernel

theorem tot4331 : totK PD2M8K2 D2M8K2.t4331 = [0, 0, 0, 117555187844, 459361652470, 283089101751, 14381462175, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
