import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2988 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2988 = true := by
  decide +kernel

theorem tot2988 : totK PA10K2 A10K2.t2988 = [0, 528753827140, 1902025210961, 1925095818052, 516090930751, 31611289403, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2989 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2989 = true := by
  decide +kernel

theorem tot2989 : totK PA10K2 A10K2.t2989 = [0, 45274709553, 848890478947, 2065542914796, 1539209827109, 363455872157, 25351274858, 0, 0, 0] := by
  decide +kernel

theorem rows2990 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2990 = true := by
  decide +kernel

theorem tot2990 : totK PA10K2 A10K2.t2990 = [0, 287401092091, 1264214752748, 1991097972600, 1239587442820, 212893329295, 5459593153, 0, 0, 0] := by
  decide +kernel

theorem rows2991 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2991 = true := by
  decide +kernel

theorem tot2991 : totK PA10K2 A10K2.t2991 = [0, 307169639377, 1513495611495, 2229546478594, 944007539522, 79474697219, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
