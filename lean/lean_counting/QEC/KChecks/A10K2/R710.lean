import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2840 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2840 = true := by
  decide +kernel

theorem tot2840 : totK PA10K2 A10K2.t2840 = [499409055073, 1825490249948, 1919029076552, 668457045669, 65502523519, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2841 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2841 = true := by
  decide +kernel

theorem tot2841 : totK PA10K2 A10K2.t2841 = [304843936410, 1431191280310, 2193114051199, 1022042046512, 84696406251, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2842 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2842 = true := by
  decide +kernel

theorem tot2842 : totK PA10K2 A10K2.t2842 = [15703692072, 505158944363, 1869549174194, 1982397350079, 537040055556, 31747192500, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2843 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2843 = true := by
  decide +kernel

theorem tot2843 : totK PA10K2 A10K2.t2843 = [509018165791, 1843067247496, 1925874025591, 551524130143, 36272339116, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
