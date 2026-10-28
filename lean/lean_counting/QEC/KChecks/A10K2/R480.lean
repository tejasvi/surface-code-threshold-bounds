import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1920 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1920 = true := by
  decide +kernel

theorem tot1920 : totK PA10K2 A10K2.t1920 = [0, 0, 252824012363, 1107844875029, 1919489991632, 1407761642373, 257404641111, 7047025452, 0, 0] := by
  decide +kernel

theorem rows1921 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1921 = true := by
  decide +kernel

theorem tot1921 : totK PA10K2 A10K2.t1921 = [0, 0, 491274956840, 1819221790762, 2030148874599, 591906898609, 23581264317, 0, 0, 0] := by
  decide +kernel

theorem rows1922 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1922 = true := by
  decide +kernel

theorem tot1922 : totK PA10K2 A10K2.t1922 = [0, 0, 122137344176, 1009805811053, 2146778559849, 1449557036651, 217457251714, 6066958478, 0, 0] := by
  decide +kernel

theorem rows1923 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1923 = true := by
  decide +kernel

theorem tot1923 : totK PA10K2 A10K2.t1923 = [0, 0, 0, 605644445534, 2045422002097, 1877771124220, 410313060308, 11910457242, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
