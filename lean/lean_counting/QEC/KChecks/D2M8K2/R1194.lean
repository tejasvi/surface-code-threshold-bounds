import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4776 = true := by
  decide +kernel

theorem tot4776 : totK PD2M8K2 D2M8K2.t4776 = [0, 0, 92861591997, 406475000896, 362692494262, 39310769474, 0, 0] := by
  decide +kernel

theorem rows4777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4777 = true := by
  decide +kernel

theorem tot4777 : totK PD2M8K2 D2M8K2.t4777 = [0, 0, 200826953316, 473645694164, 215034767231, 17318317277, 0, 0] := by
  decide +kernel

theorem rows4778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4778 = true := by
  decide +kernel

theorem tot4778 : totK PD2M8K2 D2M8K2.t4778 = [0, 0, 191181497497, 479939167277, 218647545693, 11042149229, 0, 0] := by
  decide +kernel

theorem rows4779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4779 = true := by
  decide +kernel

theorem tot4779 : totK PD2M8K2 D2M8K2.t4779 = [0, 0, 172889140466, 474957852778, 249648849646, 16776741768, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
