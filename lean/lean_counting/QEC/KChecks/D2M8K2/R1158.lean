import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4632 = true := by
  decide +kernel

theorem tot4632 : totK PD2M8K2 D2M8K2.t4632 = [0, 0, 87157149081, 160019341518, 243497958239, 308962831616, 66564545234, 1394496256] := by
  decide +kernel

theorem rows4633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4633 = true := by
  decide +kernel

theorem tot4633 : totK PD2M8K2 D2M8K2.t4633 = [0, 0, 235975120908, 501141113956, 164160171769, 5237455806, 0, 0] := by
  decide +kernel

theorem rows4634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4634 = true := by
  decide +kernel

theorem tot4634 : totK PD2M8K2 D2M8K2.t4634 = [0, 0, 54355520965, 322584906331, 424293460707, 82136418862, 1369150432, 0] := by
  decide +kernel

theorem rows4635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4635 = true := by
  decide +kernel

theorem tot4635 : totK PD2M8K2 D2M8K2.t4635 = [0, 0, 92930711933, 389040021069, 395783026268, 43157573940, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
