import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows424 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t424 = true := by
  decide +kernel

theorem tot424 : totK PA10K2 A10K2.t424 = [513450289406, 1697795822420, 1543043078653, 573547320478, 393846748437, 140909026976, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows425 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t425 = true := by
  decide +kernel

theorem tot425 : totK PA10K2 A10K2.t425 = [295030643566, 1460776667802, 2235747135232, 967507579307, 76888319121, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows426 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t426 = true := by
  decide +kernel

theorem tot426 : totK PA10K2 A10K2.t426 = [0, 605874214216, 1981633937288, 1821891812129, 482353873475, 30810868011, 0, 0, 0, 0] := by
  decide +kernel

theorem rows427 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t427 = true := by
  decide +kernel

theorem tot427 : totK PA10K2 A10K2.t427 = [505168435239, 1784688163597, 2026863864268, 763463094274, 78727762176, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
