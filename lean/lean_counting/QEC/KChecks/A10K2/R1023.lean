import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4092 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4092 = true := by
  decide +kernel

theorem tot4092 : totK PA10K2 A10K2.t4092 = [0, 286204115926, 1553160179103, 2206445291644, 753440391949, 55083815889, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4093 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4093 = true := by
  decide +kernel

theorem tot4093 : totK PA10K2 A10K2.t4093 = [0, 0, 469669404343, 1811728538833, 1786725873151, 477318780826, 30650496230, 0, 0, 0] := by
  decide +kernel

theorem rows4094 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4094 = true := by
  decide +kernel

theorem tot4094 : totK PA10K2 A10K2.t4094 = [0, 445257149950, 1746080721726, 1951659250666, 631452007706, 48666249715, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4095 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4095 = true := by
  decide +kernel

theorem tot4095 : totK PA10K2 A10K2.t4095 = [0, 279660356824, 1459235450364, 2069829198189, 747714656432, 45543540946, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
