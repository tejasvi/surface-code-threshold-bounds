import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5780 = true := by
  decide +kernel

theorem tot5780 : totK PD2M8K2 D2M8K2.t5780 = [0, 244743302269, 457176242394, 199067101969, 21400436502, 0, 0, 0] := by
  decide +kernel

theorem rows5781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5781 = true := by
  decide +kernel

theorem tot5781 : totK PD2M8K2 D2M8K2.t5781 = [0, 175775199450, 492802304570, 221521646013, 7994456143, 0, 0, 0] := by
  decide +kernel

theorem rows5782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5782 = true := by
  decide +kernel

theorem tot5782 : totK PD2M8K2 D2M8K2.t5782 = [106023797137, 302817684387, 338057865873, 152050753463, 8214505460, 0, 0, 0] := by
  decide +kernel

theorem rows5783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5783 = true := by
  decide +kernel

theorem tot5783 : totK PD2M8K2 D2M8K2.t5783 = [159599414015, 449341163376, 279974104896, 30503186154, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
