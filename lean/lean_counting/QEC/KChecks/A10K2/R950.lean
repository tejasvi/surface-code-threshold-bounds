import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3800 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3800 = true := by
  decide +kernel

theorem tot3800 : totK PA10K2 A10K2.t3800 = [0, 0, 491918945281, 1931733972660, 2016178980951, 547672913810, 32408125582, 0, 0, 0] := by
  decide +kernel

theorem rows3801 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3801 = true := by
  decide +kernel

theorem tot3801 : totK PA10K2 A10K2.t3801 = [0, 0, 117288091724, 936533410738, 2055094541799, 1525233010877, 341515931474, 20328650499, 0, 0] := by
  decide +kernel

theorem rows3802 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3802 = true := by
  decide +kernel

theorem tot3802 : totK PA10K2 A10K2.t3802 = [0, 0, 192465652475, 1098976384699, 2153918774866, 1451723714315, 247117114545, 11193583013, 0, 0] := by
  decide +kernel

theorem rows3803 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3803 = true := by
  decide +kernel

theorem tot3803 : totK PA10K2 A10K2.t3803 = [0, 0, 605984664308, 2023537893334, 1940519656411, 512194532789, 33688293268, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
