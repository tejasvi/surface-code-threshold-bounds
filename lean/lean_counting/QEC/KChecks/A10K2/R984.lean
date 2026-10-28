import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3936 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3936 = true := by
  decide +kernel

theorem tot3936 : totK PA10K2 A10K2.t3936 = [0, 0, 264357917993, 1446155272859, 2135020785181, 797194391895, 51697930226, 0, 0, 0] := by
  decide +kernel

theorem rows3937 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3937 = true := by
  decide +kernel

theorem tot3937 : totK PA10K2 A10K2.t3937 = [0, 0, 453137015736, 1472903579993, 1795725684098, 930214334366, 158889424909, 6121173289, 0, 0] := by
  decide +kernel

theorem rows3938 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3938 = true := by
  decide +kernel

theorem tot3938 : totK PA10K2 A10K2.t3938 = [0, 0, 330877078154, 1629483420345, 2221944111990, 799967740790, 44403727295, 0, 0, 0] := by
  decide +kernel

theorem rows3939 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3939 = true := by
  decide +kernel

theorem tot3939 : totK PA10K2 A10K2.t3939 = [0, 575843650046, 1934934862175, 1769791524864, 480212108296, 116108348309, 31948022301, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
