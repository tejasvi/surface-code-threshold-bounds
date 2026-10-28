import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4020 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4020 = true := by
  decide +kernel

theorem tot4020 : totK PA10K2 A10K2.t4020 = [0, 0, 480258902431, 1823311422622, 1954016798914, 568414654601, 50013658064, 0, 0, 0] := by
  decide +kernel

theorem rows4021 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4021 = true := by
  decide +kernel

theorem tot4021 : totK PA10K2 A10K2.t4021 = [0, 0, 214856499053, 1191814204695, 2089307218362, 1183889253753, 184761669980, 6121173289, 0, 0] := by
  decide +kernel

theorem rows4022 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4022 = true := by
  decide +kernel

theorem tot4022 : totK PA10K2 A10K2.t4022 = [0, 0, 614271698336, 2030752562508, 1877845111138, 474707509952, 25605627404, 0, 0, 0] := by
  decide +kernel

theorem rows4023 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4023 = true := by
  decide +kernel

theorem tot4023 : totK PA10K2 A10K2.t4023 = [0, 383428828220, 1268841561252, 1480599515508, 1092196010644, 503590258140, 50555834002, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
