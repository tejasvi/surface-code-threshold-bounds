import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4076 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4076 = true := by
  decide +kernel

theorem tot4076 : totK PA10K2 A10K2.t4076 = [0, 0, 0, 297798990022, 1399363430947, 2131297519783, 956829900591, 91805750933, 0, 0] := by
  decide +kernel

theorem rows4077 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4077 = true := by
  decide +kernel

theorem tot4077 : totK PA10K2 A10K2.t4077 = [0, 0, 0, 468236897073, 1830357876174, 2046843523782, 671585072332, 50414133861, 0, 0] := by
  decide +kernel

theorem rows4078 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4078 = true := by
  decide +kernel

theorem tot4078 : totK PA10K2 A10K2.t4078 = [0, 0, 0, 107748999220, 928117682145, 2110883007167, 1487355171023, 226738269337, 6439430839, 0] := by
  decide +kernel

theorem rows4079 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4079 = true := by
  decide +kernel

theorem tot4079 : totK PA10K2 A10K2.t4079 = [0, 0, 0, 507199742218, 1861237211407, 1981241253009, 540893775100, 22108643497, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
