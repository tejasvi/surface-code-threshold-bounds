import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5688 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5688 = true := by
  decide +kernel

theorem tot5688 : totK PA10K2 A10K2.t5688 = [0, 0, 137708441353, 756749266929, 1855816063228, 1610003353806, 321956483479, 11427838733, 0, 0] := by
  decide +kernel

theorem rows5689 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5689 = true := by
  decide +kernel

theorem tot5689 : totK PA10K2 A10K2.t5689 = [0, 0, 470121114091, 1712690119192, 1903085713113, 620882248558, 51475380808, 0, 0, 0] := by
  decide +kernel

theorem rows5690 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5690 = true := by
  decide +kernel

theorem tot5690 : totK PA10K2 A10K2.t5690 = [0, 0, 212197739899, 1414327211141, 2200007312034, 808948744012, 53438372263, 0, 0, 0] := by
  decide +kernel

theorem rows5691 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5691 = true := by
  decide +kernel

theorem tot5691 : totK PA10K2 A10K2.t5691 = [0, 0, 0, 640481985333, 2084212919273, 1615440290980, 282304803789, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
