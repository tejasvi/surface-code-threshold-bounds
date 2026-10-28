import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4144 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4144 = true := by
  decide +kernel

theorem tot4144 : totK PA10K2 A10K2.t4144 = [0, 367148160573, 1337486559555, 1780595734418, 1030874427004, 173546873073, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows4145 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4145 = true := by
  decide +kernel

theorem tot4145 : totK PA10K2 A10K2.t4145 = [0, 421735194181, 1721624450088, 1901036675490, 532150542113, 32112518205, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4146 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4146 = true := by
  decide +kernel

theorem tot4146 : totK PA10K2 A10K2.t4146 = [0, 0, 689420228412, 2202317941181, 1504533167050, 176697573712, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4147 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4147 = true := by
  decide +kernel

theorem tot4147 : totK PA10K2 A10K2.t4147 = [0, 0, 576146009172, 1883715822629, 1775315027876, 487546741807, 31987755669, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
