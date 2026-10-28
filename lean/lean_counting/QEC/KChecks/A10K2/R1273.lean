import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5092 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5092 = true := by
  decide +kernel

theorem tot5092 : totK PA10K2 A10K2.t5092 = [0, 234454346688, 1052511860230, 1794269740473, 1331723064058, 240180008226, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows5093 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5093 = true := by
  decide +kernel

theorem tot5093 : totK PA10K2 A10K2.t5093 = [0, 583209941258, 1892951306261, 1796919556974, 517501593553, 31941609474, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5094 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5094 = true := by
  decide +kernel

theorem tot5094 : totK PA10K2 A10K2.t5094 = [0, 0, 1030636270321, 2417451097093, 1155189405571, 93176710616, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5095 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5095 = true := by
  decide +kernel

theorem tot5095 : totK PA10K2 A10K2.t5095 = [0, 0, 482887831827, 1819435448208, 1869280306483, 480565596367, 31558137809, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
