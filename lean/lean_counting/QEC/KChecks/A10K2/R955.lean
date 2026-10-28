import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3820 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3820 = true := by
  decide +kernel

theorem tot3820 : totK PA10K2 A10K2.t3820 = [0, 0, 477404030452, 1545871480062, 1827494720663, 937060903597, 93442396083, 0, 0, 0] := by
  decide +kernel

theorem rows3821 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3821 = true := by
  decide +kernel

theorem tot3821 : totK PA10K2 A10K2.t3821 = [0, 0, 336967145562, 1595536387269, 2132988612009, 782418171769, 62171656476, 0, 0, 0] := by
  decide +kernel

theorem rows3822 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3822 = true := by
  decide +kernel

theorem tot3822 : totK PA10K2 A10K2.t3822 = [0, 0, 0, 474774686421, 1794618726111, 1889058718651, 501550559756, 31768748853, 0, 0] := by
  decide +kernel

theorem rows3823 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3823 = true := by
  decide +kernel

theorem tot3823 : totK PA10K2 A10K2.t3823 = [0, 0, 482403941286, 1676039738503, 1850782996035, 711492411141, 75026102165, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
