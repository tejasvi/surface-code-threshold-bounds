import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1948 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1948 = true := by
  decide +kernel

theorem tot1948 : totK PA10K2 A10K2.t1948 = [0, 380600420975, 1554544333686, 2028442374570, 890467383151, 123163814301, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows1949 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1949 = true := by
  decide +kernel

theorem tot1949 : totK PA10K2 A10K2.t1949 = [0, 210580877486, 1115647705513, 2031607215076, 1178666566417, 184664403717, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows1950 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1950 = true := by
  decide +kernel

theorem tot1950 : totK PA10K2 A10K2.t1950 = [0, 500253467170, 1853072536883, 2018716628745, 602117834158, 41567772668, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1951 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1951 = true := by
  decide +kernel

theorem tot1951 : totK PA10K2 A10K2.t1951 = [0, 216098064416, 1314277287115, 2235241146670, 1195492348234, 130953540506, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
