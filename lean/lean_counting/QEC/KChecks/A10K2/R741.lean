import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2964 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2964 = true := by
  decide +kernel

theorem tot2964 : totK PA10K2 A10K2.t2964 = [0, 0, 480878724447, 1750281743484, 2030268345093, 706178927814, 56060786809, 0, 0, 0] := by
  decide +kernel

theorem rows2965 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2965 = true := by
  decide +kernel

theorem tot2965 : totK PA10K2 A10K2.t2965 = [0, 0, 570315010427, 1950999238428, 1843294916517, 414232050045, 11997355697, 0, 0, 0] := by
  decide +kernel

theorem rows2966 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2966 = true := by
  decide +kernel

theorem tot2966 : totK PA10K2 A10K2.t2966 = [0, 0, 0, 806664646508, 2266714911252, 1487826075539, 217043516580, 6318667960, 0, 0] := by
  decide +kernel

theorem rows2967 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2967 = true := by
  decide +kernel

theorem tot2967 : totK PA10K2 A10K2.t2967 = [0, 0, 446335997791, 1598122596812, 1991908419956, 819453104589, 67827945323, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
