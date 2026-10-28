import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4368 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4368 = true := by
  decide +kernel

theorem tot4368 : totK PA10K2 A10K2.t4368 = [0, 0, 249045368514, 1257913307525, 2116866622198, 1034838845999, 104071152193, 0, 0, 0] := by
  decide +kernel

theorem rows4369 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4369 = true := by
  decide +kernel

theorem tot4369 : totK PA10K2 A10K2.t4369 = [0, 0, 77221818893, 625152327340, 1775690860503, 1628250295807, 451287104288, 30650496230, 0, 0] := by
  decide +kernel

theorem rows4370 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4370 = true := by
  decide +kernel

theorem tot4370 : totK PA10K2 A10K2.t4370 = [0, 0, 498671546204, 1835662767293, 1906685825490, 513308351625, 31608797364, 0, 0, 0] := by
  decide +kernel

theorem rows4371 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4371 = true := by
  decide +kernel

theorem tot4371 : totK PA10K2 A10K2.t4371 = [0, 0, 191980019778, 1386576791868, 2234396646571, 835162215698, 59823752816, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
