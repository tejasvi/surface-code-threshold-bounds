import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4912 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4912 = true := by
  decide +kernel

theorem tot4912 : totK PA10K2 A10K2.t4912 = [197161727086, 1163454705157, 2131799875881, 1244521909615, 210111132182, 15171143123, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4913 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4913 = true := by
  decide +kernel

theorem tot4913 : totK PA10K2 A10K2.t4913 = [100524798383, 694655155184, 1816643927736, 1725909589846, 399595268754, 16597605730, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4914 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4914 = true := by
  decide +kernel

theorem tot4914 : totK PA10K2 A10K2.t4914 = [430869192079, 1669807774802, 1960632958837, 663801371025, 52232171148, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4915 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4915 = true := by
  decide +kernel

theorem tot4915 : totK PA10K2 A10K2.t4915 = [276249092272, 1501915271126, 2058382958929, 799700919910, 60955399093, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
