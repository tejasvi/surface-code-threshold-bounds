import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6656 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6656 = true := by
  decide +kernel

theorem tot6656 : totK PA10K2 A10K2.t6656 = [0, 527390943100, 1840660587782, 1910169152277, 660054965287, 107716245969, 5546304973, 0, 0, 0] := by
  decide +kernel

theorem rows6657 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6657 = true := by
  decide +kernel

theorem tot6657 : totK PA10K2 A10K2.t6657 = [303501126640, 1096124828449, 1589381750242, 1424228582580, 551645019391, 50491866487, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6658 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6658 = true := by
  decide +kernel

theorem tot6658 : totK PA10K2 A10K2.t6658 = [456053228344, 1801622182260, 2011414149025, 565689304258, 32040661968, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6659 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6659 = true := by
  decide +kernel

theorem tot6659 : totK PA10K2 A10K2.t6659 = [0, 648682882322, 2046122780854, 1718684563802, 404792956335, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
