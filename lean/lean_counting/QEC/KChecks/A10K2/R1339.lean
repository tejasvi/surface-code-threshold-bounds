import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5356 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5356 = true := by
  decide +kernel

theorem tot5356 : totK PA10K2 A10K2.t5356 = [0, 0, 0, 688127518141, 2210960272851, 1871680650637, 327043421195, 6853348008, 0, 0] := by
  decide +kernel

theorem rows5357 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5357 = true := by
  decide +kernel

theorem tot5357 : totK PA10K2 A10K2.t5357 = [0, 0, 0, 425840627540, 1683007214641, 2025053180566, 704955033659, 55262340418, 0, 0] := by
  decide +kernel

theorem rows5358 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5358 = true := by
  decide +kernel

theorem tot5358 : totK PA10K2 A10K2.t5358 = [0, 0, 0, 401426142260, 1698651298233, 1990000866431, 667576089694, 49649068552, 0, 0] := by
  decide +kernel

theorem rows5359 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5359 = true := by
  decide +kernel

theorem tot5359 : totK PA10K2 A10K2.t5359 = [0, 0, 0, 111663328169, 909535638117, 2080272199733, 1394658923357, 246694035363, 7007974415, 0] := by
  decide +kernel

end QECKChecks.A10K2
