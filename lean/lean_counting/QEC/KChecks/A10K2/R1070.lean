import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4280 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4280 = true := by
  decide +kernel

theorem tot4280 : totK PA10K2 A10K2.t4280 = [0, 0, 305486285361, 1562318120138, 2241013948536, 869647629692, 62639122019, 0, 0, 0] := by
  decide +kernel

theorem rows4281 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4281 = true := by
  decide +kernel

theorem tot4281 : totK PA10K2 A10K2.t4281 = [0, 0, 234814154535, 1068642446405, 1947625770536, 1446749093447, 226738269337, 6439430839, 0, 0] := by
  decide +kernel

theorem rows4282 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4282 = true := by
  decide +kernel

theorem tot4282 : totK PA10K2 A10K2.t4282 = [0, 0, 490174267241, 1836549487657, 2008002876353, 549672731613, 22108643497, 0, 0, 0] := by
  decide +kernel

theorem rows4283 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4283 = true := by
  decide +kernel

theorem tot4283 : totK PA10K2 A10K2.t4283 = [0, 0, 122511336145, 1047360644617, 2164259479928, 1353470062445, 208296867606, 6021244195, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
