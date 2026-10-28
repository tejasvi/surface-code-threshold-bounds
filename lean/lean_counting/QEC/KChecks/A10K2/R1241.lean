import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4964 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4964 = true := by
  decide +kernel

theorem tot4964 : totK PA10K2 A10K2.t4964 = [117105040969, 294239939537, 474553866121, 1468193942857, 1932982265815, 732288083005, 56100664475, 0, 0, 0] := by
  decide +kernel

theorem rows4965 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4965 = true := by
  decide +kernel

theorem tot4965 : totK PA10K2 A10K2.t4965 = [463902755304, 1818857191342, 1960771105613, 499215678802, 25686058060, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4966 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4966 = true := by
  decide +kernel

theorem tot4966 : totK PA10K2 A10K2.t4966 = [219519362361, 1114425721005, 1930292375688, 1194189512283, 234510547799, 20070762815, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4967 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4967 = true := by
  decide +kernel

theorem tot4967 : totK PA10K2 A10K2.t4967 = [112037851608, 728534151567, 1856181182338, 1634314908846, 339578868008, 10760911071, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
