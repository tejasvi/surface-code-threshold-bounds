import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7616 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7616 = true := by
  decide +kernel

theorem tot7616 : totK PA10K2 A10K2.t7616 = [0, 0, 0, 511296585505, 1904389575286, 2079521970213, 542127598683, 18515547658, 0, 0] := by
  decide +kernel

theorem rows7617 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7617 = true := by
  decide +kernel

theorem tot7617 : totK PA10K2 A10K2.t7617 = [0, 0, 282573750534, 1106552140705, 1672211923171, 1372909091960, 542936732699, 50432252117, 0, 0] := by
  decide +kernel

theorem rows7618 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7618 = true := by
  decide +kernel

theorem tot7618 : totK PA10K2 A10K2.t7618 = [0, 0, 399796758777, 1673204531806, 2146137943870, 825898657307, 69991709124, 0, 0, 0] := by
  decide +kernel

theorem rows7619 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7619 = true := by
  decide +kernel

theorem tot7619 : totK PA10K2 A10K2.t7619 = [0, 0, 161424244126, 892013693242, 1981727743012, 1638264925314, 327964247666, 11991740650, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
