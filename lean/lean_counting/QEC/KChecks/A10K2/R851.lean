import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3404 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3404 = true := by
  decide +kernel

theorem tot3404 : totK PA10K2 A10K2.t3404 = [0, 0, 0, 0, 542186257868, 1828764643030, 1743664942542, 479302778684, 31082886609, 0] := by
  decide +kernel

theorem rows3405 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3405 = true := by
  decide +kernel

theorem tot3405 : totK PA10K2 A10K2.t3405 = [0, 0, 0, 509026996888, 1736280204964, 1750053822692, 591108318101, 55879297308, 0, 0] := by
  decide +kernel

theorem rows3406 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3406 = true := by
  decide +kernel

theorem tot3406 : totK PA10K2 A10K2.t3406 = [0, 0, 0, 210579259701, 1377220728297, 2156085531768, 786275689624, 51626803747, 0, 0] := by
  decide +kernel

theorem rows3407 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3407 = true := by
  decide +kernel

theorem tot3407 : totK PA10K2 A10K2.t3407 = [0, 0, 0, 470942421151, 1481622112637, 1700594443979, 913223761923, 167715549196, 6121173289, 0] := by
  decide +kernel

end QECKChecks.A10K2
