import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14780 = true := by
  decide +kernel

theorem tot14780 : totK PD2M8K2 D2M8K2.t14780 = [92999530293, 368937675196, 370007124631, 70354732263, 1267860612, 0, 0, 0] := by
  decide +kernel

theorem rows14781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14781 = true := by
  decide +kernel

theorem tot14781 : totK PD2M8K2 D2M8K2.t14781 = [0, 263572525400, 492643266930, 144254576190, 3693668399, 0, 0, 0] := by
  decide +kernel

theorem rows14782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14782 = true := by
  decide +kernel

theorem tot14782 : totK PD2M8K2 D2M8K2.t14782 = [0, 186641657759, 465730943504, 224928460454, 17066492788, 0, 0, 0] := by
  decide +kernel

theorem rows14783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14783 = true := by
  decide +kernel

theorem tot14783 : totK PD2M8K2 D2M8K2.t14783 = [0, 168228683816, 445602045956, 280958722489, 28472831638, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
