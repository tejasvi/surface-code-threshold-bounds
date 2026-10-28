import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3560 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3560 = true := by
  decide +kernel

theorem tot3560 : totK PA10K2 A10K2.t3560 = [0, 0, 498212526433, 1848064359829, 1825394735926, 475714241563, 30831673886, 0, 0, 0] := by
  decide +kernel

theorem rows3561 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3561 = true := by
  decide +kernel

theorem tot3561 : totK PA10K2 A10K2.t3561 = [0, 460078346494, 1650657541627, 1892770021358, 767626155257, 76719271263, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3562 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3562 = true := by
  decide +kernel

theorem tot3562 : totK PA10K2 A10K2.t3562 = [0, 285599711294, 1457821403815, 2079631984432, 790389470479, 59748166096, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3563 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3563 = true := by
  decide +kernel

theorem tot3563 : totK PA10K2 A10K2.t3563 = [0, 202921703859, 986485656360, 1884213394376, 1310305229900, 242123330277, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
